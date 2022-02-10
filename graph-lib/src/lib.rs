use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    str::FromStr, slice::Iter,
};

use itertools::Itertools;

use log::trace;

macro_rules! err {
    ($($arg:tt)+) => {
        #[cfg(feature = "log_error")]
        log::error!($($arg)+);
    };
}

pub enum Error {
    NotPoint,
    ParseError,
    NotEnough,
    NotMinBy
}

pub struct Point<K, T> {
    v: T,
    childs: HashMap<K, T>,
}

impl<K: Hash + Eq, T> Point<K, T> {
    pub fn new(v: T) -> Point<K, T> {
        Point {
            v,
            childs: HashMap::new(),
        }
    }
    pub fn add(&mut self, l: K, v: T) -> Option<T> {
        self.childs.insert(l, v)
    }
    pub fn inner(self) -> T {
        self.v
    }
}


pub enum TpDirected{
    Deep,
    Width
}

pub type Orderer<K, T> = fn(&(&K, &Point<K, T>), &(&K, &Point<K, T>))->std::cmp::Ordering;

pub struct GraphIter<K, T>{
    position: K,
    visited: HashSet<K>,
    graph: Graph<K, T>,
    tp: TpDirected,
    f: Option<Orderer<K, T>>,
    ordered: Option<Vec<K>>
}

impl<K: PartialOrd + Clone, T> GraphIter<K, T>{
    pub fn new(graph: Graph<K, T>, tp: TpDirected, f: Orderer<K, T> )->Result<GraphIter<K, T>, Error>{
        let min = match graph.get_points().iter().min_by(f){
            Some(v)=>v,
            None=>return Err(Error::NotMinBy)
        };
        Ok(GraphIter{
            position: min.0.clone(),
            visited: HashSet::new(),
            graph,
            tp,
            f: Some(f),
            ordered: None
        })
    }
}

impl<K, T> Iterator for GraphIter<K, T>{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let mut order = Vec::new();
        if let Some(f) = self.f {
            if self.ordered.is_none(){
                order = self.graph.get_points().iter().sorted_by(f).collect();
            };
        };
        
    }
}

pub struct Graph<K, T> {
    points: HashMap<K, Point<K, T>>,
    directed: bool,
}

impl<K, T> Graph<K, T>{
    pub fn get_points(&self)->&HashMap<K, Point<K, T>>{
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
    pub fn point(&mut self, k: K, v: T) -> Option<Point<K, T>> {
        self.points.insert(k, Point::new(v))
    }
    pub fn link(&mut self, from: K, to: K, v: T) -> Result<(), Error> {
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
    
}

impl<K: ToString, T:ToString> ToString for Graph<K,T>{
    fn to_string(&self) -> String {
        let mut points = String::new();
        let mut links = String::new();

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
                Some(v)=>v,
                None=>return Err(Error::NotEnough)
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
            while let Some(d) = spl.next(){
                if f{
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
            };
            let v = match T::from_str(buff.as_str()){
                Ok(v)=>{v},
                Err(_e)=>{
                    err!("Original Parse error: {:?}", _e);
                    return Err(Error::ParseError);
                }
            };
            match k2{
                Some(to)=>{
                    match g.link(from, to, v){
                        Ok(_)=>{},
                        Err(e)=>{
                            err!("Original Parse error: {:?}", e);
                            return Err(e);
                        }
                    }
                }
                None=>{
                    g.point(from, v);
                }
            };
            
        }
        Ok(g)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
