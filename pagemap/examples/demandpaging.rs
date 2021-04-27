//! Simple demonstration of the crate: it showcases Linux' demand paging, by checking
//! `/proc/self/maps` and `/proc/<PID>/pagemap` before and after writing to a page allocated via
//! `mmap(2)`, to observe the physical frame allocation.
//!
//! Mind the peculiarities regarding permissions and `CAP_SYS_ADMIN`, also documented here:
//! https://www.kernel.org/doc/Documentation/vm/pagemap.txt

use pagemap::{PageMap, PageMapError};

fn main() -> Result<(), PageMapError> {
    let pid = std::process::id() as u64;

    // Instantiate a new pagemap::PageMap.
    let mut pm = PageMap::new(pid)?;

    // Allocate a page through `mmap(2)`.
    let ptr = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            pagemap::page_size()? as usize,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
            -1,
            0,
        )
    };
    assert_ne!(ptr, std::ptr::null_mut(), "mmap(2) failed");
    eprintln!("ptr = {:#?}", ptr);

    // Find the VMA related to the allocation above.
    let vma = pm
        .maps()?
        .into_iter()
        .find(|me| me.memory_region().contains(ptr as u64))
        .expect("mapping not found")
        .memory_region();
    eprintln!("vma = {}", vma);

    // Find the pagemap entries related with the pages of this VMA.
    let pagemap_entries = pm.pagemap_region(&vma)?;
    // Since we allocated a single page, we expect a single PageMapEntry as well.
    assert_eq!(1, pagemap_entries.len());
    let pagemap_entry = pagemap_entries[0];
    eprintln!("pagemap_entry (before)\t= {}", pagemap_entry);

    // Since we have not written to the allocated page, and because of Linux' demand-paging, we
    // expect that no physical frame will have been allocated for this page.
    assert!(!pagemap_entry.present() && !pagemap_entry.swapped());

    // Now, let's write to the allocated page...
    unsafe { libc::memset(ptr, 0xff, pagemap::page_size()? as usize) };

    // ...and read `/proc/self/pagemap` again.
    let pagemap_entry = pm.pagemap_region(&vma)?[0];
    eprintln!("pagemap_entry (after)\t= {}", pagemap_entry);

    // This time, the physical frame should be present!
    assert!(pagemap_entry.present());

    Ok(())
}
