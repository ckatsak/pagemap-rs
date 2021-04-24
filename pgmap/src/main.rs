use pagemap::{PageMap, PageMapError};

fn parse_args() -> u64 {
    std::env::args()
        .nth(1)
        .expect("Usage: pgmap <PID>")
        .parse()
        .expect("<PID> must be a valid integer of a running process")
}

fn main() -> Result<(), PageMapError> {
    let pid = parse_args();

    let mut pm = PageMap::new(pid)?;
    let entries = pm.pagemap()?;
    entries.iter().for_each(|e| {
        eprintln!("-> {}", e.0);
        e.1.iter().filter(|&pme| pme.present()).for_each(|pme| {
            eprintln!("\t- {}", pme);
        });
    });
    eprintln!("\n-> USS = {} bytes", pagemap::uss(pid)?);

    Ok(())
}
