use bitflags::bitflags;

bitflags! {
    /// kpageflags as defined in Linux, at `include/uapi/linux/kernel-page-flags.h`.
    pub struct KPageFlags: u64 {
        const KPF_LOCKED        = 1 << 0;
        const KPF_ERROR         = 1 << 1;
        const KPF_REFERENCED    = 1 << 2;
        const KPF_UPTODATE      = 1 << 3;
        const KPF_DIRTY         = 1 << 4;
        const KPF_LRU           = 1 << 5;
        const KPF_ACTIVE        = 1 << 6;
        const KPF_SLAB          = 1 << 7;
        const KPF_WRITEBACK     = 1 << 8;
        const KPF_RECLAIM       = 1 << 9;
        const KPF_BUDDY         = 1 << 10;

        const KPF_MMAP          = 1 << 11;
        const KPF_ANON          = 1 << 12;
        const KPF_SWAPCACHE     = 1 << 13;
        const KPF_SWAPBACKED    = 1 << 14;
        const KPF_COMPOUND_HEAD = 1 << 15;
        const KPF_COMPOUND_TAIL = 1 << 16;
        const KPF_HUGE          = 1 << 17;
        const KPF_UNEVICTABLE   = 1 << 18;
        const KPF_HWPOISON      = 1 << 19;
        const KPF_NOPAGE        = 1 << 20;

        const KPF_KSM           = 1 << 21;
        const KPF_THP           = 1 << 22;
        const KPF_OFFLINE       = 1 << 23;
        const KPF_ZERO_PAGE     = 1 << 24;
        const KPF_IDLE          = 1 << 25;
        const KPF_PGTABLE       = 1 << 26;
    }
}

impl std::convert::From<u64> for KPageFlags {
    fn from(v: u64) -> Self {
        KPageFlags::from_bits_truncate(v)
    }
}

macro_rules! fn_get_bit {
    ($fn:ident, $bit:ident) => {
        /// Returns `Some(true)` if the [corresponding bit][bits] is set; `Some(false)` otherwise.
        /// It returns `None` if `/proc/kpageflags` could not be read for the page at hand.
        ///
        /// [bits]: struct.KPageFlags.html#impl
        #[inline(always)]
        pub fn $fn(&self) -> Option<bool> {
            self.kpgfl.map(|v| v.contains(KPageFlags::$bit))
        }
    };
}
