use pagemap::PageMap;

fn parse_args() -> u64 {
    std::env::args().nth(1).unwrap().parse().unwrap() // FIXME
}

fn main() -> anyhow::Result<()> {
    let pid = parse_args();

    let mut pm = PageMap::new(pid)?;
    let entries = pm.pagemap()?;
    //eprintln!("\n\n{:#?}\n", entries);
    entries.iter().for_each(|e| {
        eprintln!("-> {}", e.0);
        e.1.iter().filter(|&pme| pme.present()).for_each(|pme| {
            eprintln!("\t- {}", pme);
        });
    });

    Ok(())
}
