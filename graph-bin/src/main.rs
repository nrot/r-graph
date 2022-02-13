use std::{str::FromStr, fs::File, io::Read};

use graph_lib::{self, Graph, GraphIter};
use simple_logger;

fn main() {
    simple_logger::init_with_level(if cfg!(debug_assertions) {
        log::Level::Debug
    } else {
        log::Level::Info
    })
    .unwrap();

    let g: Graph<usize, String> = {
        let mut buff = Vec::new();
        File::open("./datas/first.tgf").unwrap().read_to_end(&mut buff).unwrap();
        Graph::from_str(&String::from_utf8(buff).unwrap()).unwrap()
    };
    let it = GraphIter::new(g, 1, graph_lib::TpDirected::Width);
    for (k, p) in it{
        log::info!("Point name: {}; Value: {};",k, p.inner());
        for (c, _) in p.childs().iter(){
            log::info!("\tLink to: {c}");
        };
    }
}
