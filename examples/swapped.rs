//! Simple demonstration of the crate: for all currently running processes, this example binary
//! prints the entries read from `/proc/<PID>/pagemap` that are currently swapped, after retrieving
//! their respective memory mappings from `/proc/<PID>/maps`.
//!
//! Mind that race conditions related to processes spawning and dying during the lifetime of this
//! program are not handled, as they are considered to be out of the scope of this example.
//! Therefore, it is quite possible that this program's execution fails as it is currently written.
//!
//! Also mind the peculiarities regarding permissions and `CAP_SYS_ADMIN`, also documented here:
//! https://www.kernel.org/doc/Documentation/vm/pagemap.txt

use std::io::Read;

use pagemap::{PageMap, PageMapError};

fn main() -> Result<(), PageMapError> {
    let mut comm = String::with_capacity(16);

    // Loop through the contents of `/proc/`.
    for dirent in std::fs::read_dir("/proc")? {
        comm.clear();

        // Skip any entry that does not look like a valid PID.
        let mut path = dirent?.path();
        let pid = match path.file_name() {
            Some(name) => match name.to_string_lossy().parse::<u64>() {
                Ok(pid) => pid,
                Err(_) => continue,
            },
            None => continue,
        };

        // Read and print process' name along with its PID.
        path.push("comm");
        let _ = std::fs::File::open(&path)?.read_to_string(&mut comm)?;
        println!("{}({}):", comm.trim_end(), pid);

        // Instantiate a new pagemap::PageMap.
        let mut pm = PageMap::new(pid)?;
        // For each mapping of the process (stored in MapsEntry through `/proc/$pid/maps`), gather
        // the PageMapEntry of each page (through `/proc/$pid/pagemap`).
        // Note that, if permitted, each PageMapEntry will also be populated with information from
        // `/proc/kpagecount` and `/proc/kpageflags`.
        let entries = pm.pagemap()?;
        // Iterate through each MapsEntry...
        entries.iter().for_each(|e| {
            // ...and then loop through each PageMapEntry (one for each page in the MapsEntry),
            // filtering out any page that appears not be swapped...
            e.1.iter().filter(|&pme| pme.swapped()).for_each(|pme| {
                // ...and printing the rest of them.
                println!("\t- {}", pme);
            });
        });
    }

    Ok(())
}
