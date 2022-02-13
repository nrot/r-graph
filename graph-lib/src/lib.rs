use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    str::FromStr,
};

#[cfg(feature = "log_error")]
use log::trace;

macro_rules! err {
    ($($arg:tt)+) => {
        #[cfg(feature = "log_error")]
        log::error!($($arg)+);
    };
}

#[derive(Debug)]
pub enum Error {
    NotPoint,
    ParseError,
    NotEnough,
    NotMinBy,
}

#[derive(Debug, Clone)]
pub struct Point<K: Clone, T: Clone> {
    v: T,
    childs: HashMap<K, T>,
}

impl<K: Hash + Eq + Clone, T: Clone> Point<K, T> {
    pub fn new(v: T) -> Point<K, T> {
        Point {
            v,
            childs: HashMap::new(),
        }
    }
    pub fn add(&mut self, l: K, v: T) -> Option<T> {
        self.childs.insert(l, v)
    }
    pub fn inner(&self) -> &T {
        &self.v
    }
    pub fn remove_link(&mut self, k: &K) -> Option<T> {
        self.childs.remove(&k)
    }
    pub fn childs(&self)->&HashMap<K, T>{
        &self.childs
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TpDirected {
    Deep,
    Width,
}

#[derive(Debug, Clone)]
pub struct GraphIter<K: Clone, T: Clone> {
    position: K,
    visited: HashSet<K>,
    graph: Graph<K, T>,
    tp: TpDirected,
    stack: Vec<K>,
}

impl<K: Hash + Eq + Clone + Debug, T: Clone + Debug> GraphIter<K, T> {
    pub fn new(graph: Graph<K, T>, start: K, tp: TpDirected) -> GraphIter<K, T> {
        GraphIter {
            position: start,
            visited: HashSet::new(),
            graph,
            tp,
            stack: Vec::new(),
        }
    }

    fn recursive_deep(&mut self, k: K) -> Option<K> {
        if let Some(p) = self.graph.get_point(&k) {
            if p.childs.is_empty() {
                if let Some(n) = self.stack.pop() {
                    self.recursive_deep(n)
                } else {
                    None
                }
            } else {
                let c = p
                    .childs
                    .iter()
                    .find_map(|(k, _)| match self.visited.contains(k) {
                        true => None,
                        false => Some(k),
                    });
                if let Some(c) = c {
                    self.stack.push(c.clone());
                    Some(c.clone())
                } else {
                    if let Some(n) = self.stack.pop() {
                        self.recursive_deep(n)
                    } else {
                        None
                    }
                }
            }
        } else {
            None
        }
    }

    fn next_deep(&mut self) -> Option<(K, Point<K, T>)> {
        let p = self.graph.get_point(&self.position).cloned();
        log::trace!("Now point: {:?}", &p);
        if self.stack.is_empty() && self.visited.is_empty() {
            self.stack.push(self.position.clone());
            return match p {
                Some(p) => Some((self.position.clone(), p)),
                None => None,
            };
        };
        if let Some(_) = p {
            self.visited.insert(self.position.clone());
            match self.recursive_deep(self.position.clone()) {
                Some(k) => {
                    self.position = k.clone();
                    match self.graph.get_point(&k).cloned() {
                        Some(p) => Some((k, p)),
                        None => None,
                    }
                }
                None => None,
            }
        } else {
            None
        }
    }
    fn next_width(&mut self) -> Option<(K, Point<K, T>)> {
        if self.stack.is_empty() && self.visited.is_empty() {
            self.stack.push(self.position.clone())
        }
        if self.stack.is_empty() {
            return None;
        };
        self.position = self.stack.get(0).unwrap().clone();
        if let Some(p) = self.graph.get_point(&self.position) {
            log::trace!("Now point: {:?}", &p);
            self.visited.insert(self.position.clone());
            self.stack.extend(p.childs.iter().filter_map(
                |(k, _)| match self.visited.contains(k) {
                    true => None,
                    false => Some(k.clone()),
                },
            ));
            self.stack.remove(0);
            match self.graph.get_point(&self.position).cloned() {
                Some(p) => Some((self.position.clone(), p)),
                None => None,
            }
        } else {
            None
        }
    }
}

impl<K: Hash + Eq + Clone + Debug, T: Clone + Debug> Iterator for GraphIter<K, T> {
    type Item = (K, Point<K, T>);
    fn next(&mut self) -> Option<Self::Item> {
        match self.tp {
            TpDirected::Deep => self.next_deep(),
            TpDirected::Width => self.next_width(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Graph<K: Clone, T: Clone> {
    points: HashMap<K, Point<K, T>>,
    ///Ориентированный или не ориентированный  граф. true - ориентированный. false - не ориентированный .
    directed: bool,
}

impl<K: Clone, T: Clone> Graph<K, T> {
    pub fn get_points(&self) -> &HashMap<K, Point<K, T>> {
        &self.points
    }
}

impl<K: Hash + Eq + Clone, T: Clone> Graph<K, T> {
    pub fn new(directed: bool) -> Graph<K, T> {
        Graph {
            directed,
            points: HashMap::new(),
        }
    }
    pub fn get_point(&self, k: &K) -> Option<&Point<K, T>> {
        self.points.get(&k)
    }
    pub fn get_childs(&self, k: &K) -> Option<&HashMap<K, T>> {
        return match self.get_point(k) {
            Some(p) => Some(&p.childs),
            None => None,
        };
    }
    pub fn add_point(&mut self, k: K, v: T) -> Option<Point<K, T>> {
        self.points.insert(k, Point::new(v))
    }
    pub fn add_link(&mut self, from: K, to: K, v: T) -> Result<(), Error> {
        if !self.directed {
            match self.points.get_mut(&to) {
                Some(p) => p.add(from.clone(), v.clone()),
                None => return Err(Error::NotPoint),
            };
        }
        match self.points.get_mut(&from) {
            Some(p) => p.add(to.clone(), v.clone()),
            None => return Err(Error::NotPoint),
        };
        Ok(())
    }
    pub fn remove_point(&mut self, k: &K) -> Option<Point<K, T>> {
        let r = self.points.remove(k);
        let _: Vec<_> = self
            .points
            .iter_mut()
            .map(|(_, p)| {
                p.remove_link(k);
                0
            })
            .collect();
        r
    }
    pub fn remove_link(&mut self, from: &K, to: &K) -> Option<T> {
        let r = if let Some(p) = self.points.get_mut(from) {
            p.remove_link(to)
        } else {
            None
        };
        if !self.directed {
            if let Some(p) = self.points.get_mut(to) {
                p.remove_link(from);
            };
        };
        r
    }
}

impl<K: ToString + Clone, T: ToString + Clone> ToString for Graph<K, T> {
    fn to_string(&self) -> String {
        let mut points = String::new();
        let mut links = String::new();
        let _: Vec<u8> = self
            .points
            .iter()
            .map(|(k, p)| {
                let from = k.to_string();
                points.push_str(format!("{} {}", from, p.v.to_string()).as_str());
                let _: Vec<u8> = p
                    .childs
                    .iter()
                    .map(|(t, v)| {
                        links.push_str(
                            format!("{} {} {}", from, t.to_string(), v.to_string()).as_str(),
                        );
                        0
                    })
                    .collect();
                0
            })
            .collect();
        points + &links
    }
}

impl<K: Hash + Eq + FromStr + Clone, T: FromStr + Clone> FromStr for Graph<K, T> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut g = Graph::new(true);
        for s in String::from(s).split("\n") {
            if s.starts_with("#") || s.is_empty() {
                continue;
            };
            let mut spl = s.split(char::is_whitespace);
            let d = match spl.next() {
                Some(v) => v,
                None => return Err(Error::NotEnough),
            };
            let from = match K::from_str(d) {
                Ok(v) => v,
                Err(_e) => {
                    err!("Original Parse error: {:?}", _e);
                    return Err(Error::ParseError);
                }
            };

            let mut buff = String::new();
            let mut k2: Option<K> = None;
            let mut f = true;
            while let Some(d) = spl.next() {
                if f {
                    f = false;
                    match K::from_str(d) {
                        Ok(v) => {
                            k2 = Some(v);
                            continue;
                        }
                        Err(_e) => {
                            err!("Original Parse error: {:?}", _e);
                        }
                    };
                };
                buff.push_str(d);
            }
            let v = match T::from_str(buff.as_str()) {
                Ok(v) => v,
                Err(_e) => {
                    err!("Original Parse error: {:?}", _e);
                    return Err(Error::ParseError);
                }
            };
            match k2 {
                Some(to) => match g.add_link(from, to, v) {
                    Ok(_) => {}
                    Err(e) => {
                        err!("Original Parse error: {:?}", e);
                        return Err(e);
                    }
                },
                None => {
                    g.add_point(from, v);
                }
            };
        }
        Ok(g)
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::{Graph, GraphIter};

    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
    #[test]
    fn from_str() {
        let d = r#"1 First
2 Second
1 2 FLink
# Comment
"#;
        let g: Graph<usize, String> = Graph::from_str(d).unwrap();
        let mut i = GraphIter::new(g, 1, crate::TpDirected::Deep);
        assert_eq!("First", i.next().unwrap().1.v);
        assert_eq!("Second", i.next().unwrap().1.v);
        assert!(i.next().is_none());
    }
    #[test]
    fn recursive_check() {
        let s = r#"1 First
2 Second
1 2 FLink
2 1 SLink
"#;
        let g: Graph<_, String> = Graph::from_str(s).unwrap();
        let mut i = GraphIter::new(g, 1, crate::TpDirected::Deep);
        assert_eq!("First", i.next().unwrap().1.v);
        assert_eq!("Second", i.next().unwrap().1.v);
        assert!(i.next().is_none());
    }
    #[test]
    fn width_test() {
        let s = r#"1 First
2 Second
3 Third
1 2 FLink
1 3 FThird"#;
        let g: Graph<_, String> = Graph::from_str(s).unwrap();
        let mut i = GraphIter::new(g, 1, crate::TpDirected::Width);
        assert_eq!("First", i.next().unwrap().1.v);
        let s = i.next().unwrap().1.v;
        let sa: String = if &s == "Third" {
            "Second".into()
        } else if &s == "Second" {
            "Third".into()
        } else {
            panic!("Not Third or Second");
        };
        assert_eq!(sa, i.next().unwrap().1.v);
        assert!(i.next().is_none());
    }
    #[test]
    fn add_remove_directed_test() {
        let mut g = Graph::new(true);
        g.add_point(1, "First");
        g.add_point(2, "Second");
        g.add_link(1, 2, "FLink").unwrap();
        g.add_point(3, "Third");
        g.add_link(2, 3, "FSecond").unwrap();
        g.add_link(3, 1, "Save link").unwrap();
        g.remove_point(&2);
        let mut i = GraphIter::new(g.clone(), 1, crate::TpDirected::Width);
        assert_eq!("First", i.next().unwrap().1.v);
        assert!(i.next().is_none());

        let mut i = GraphIter::new(g.clone(), 3, crate::TpDirected::Width);
        assert_eq!("Third", i.next().unwrap().1.v);
        assert_eq!("First", i.next().unwrap().1.v);
        assert!(i.next().is_none());
    }
}
