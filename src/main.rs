use parts::*;

fn main() {
    let buff = std::fs::File::open("scratch/test_parts").unwrap();
    let gpt = Gpt::from_reader(buff, 512);
    dbg!(&gpt);
    match gpt {
        Err(e) => {
            println!("{}", e);
            dbg!(e);
        }
        _ => (),
    }
}
