//! Simple demonstration of the crate: it prints the entries read from `/proc/<PID>/pagemap` that
//! are currently present, after retrieving the memory mappings from `/proc/<PID>/maps`.
//!
//! Mind the peculiarities regarding permissions and `CAP_SYS_ADMIN`, also documented here:
//! https://www.kernel.org/doc/Documentation/vm/pagemap.txt

use pagemap::{PageMap, PageMapError};

/// Retrieve a PID from the command line, in a quick and dirty way.
fn parse_args() -> u64 {
    std::env::args()
        .nth(1)
        .expect("Usage: cargo run --example present <PID>")
        .parse()
        .expect("<PID> must be a valid integer of a running process")
}

fn main() -> Result<(), PageMapError> {
    let pid = parse_args();

    // Instantiate a new pagemap::PageMap.
    let mut pm = PageMap::new(pid)?;
    // For each mapping of the process (stored in MapsEntry through `/proc/$pid/maps`), gather the
    // PageMapEntry of each page (through `/proc/$pid/pagemap`).
    // Note that, if permitted, each PageMapEntry will also be populated with information from
    // `/proc/kpagecount` and `/proc/kpageflags`.
    let entries = pm.pagemap()?;
    // Iterate through each MapsEntry...
    entries.iter().for_each(|e| {
        // ...printing it...
        eprintln!("-> {}", e.0);
        // ...and then loop through each PageMapEntry (one per page of the MapsEntry), filtering
        // out any page that appears to not be present...
        e.1.iter().filter(|&pme| pme.present()).for_each(|pme| {
            // ...and printing the rest of them.
            eprintln!("\t- {}", pme);
        });
    });

    Ok(())
}
