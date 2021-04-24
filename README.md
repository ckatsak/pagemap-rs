# pagemap-rs

## Thoughts & `TODO`s

- [ ] Documentation

- [ ] `kpagecount` and `kpageflags`

`/proc/kpagecount` and `/proc/kpageflags` can only be read with `CAP_SYS_ADMIN`
whereas `/proc/PID/maps` can be read by everyone and `/proc/PID/pagemap` can be
read but returns zeroes rather than the true values.

This crate (for now) allows a `PageMap::pagemap(PID)` (which accesses all of
these files) even without the `CAP_SYS_ADMIN`: it returns only the results from
reading `/proc/PID/maps` and the (_zeroed_) values from `/proc/PID/pagemap`,
while it will __silently skip__ reading `/proc/{kpagecount,kpageflags}`.

In addition, methods like `PageMap::kpagecount` and `PageMap::kpageflags`
merely return an error indicating that accessing these files failed.

`PageMap`s constructed before the `CAP_SYS_ADMIN` has been raised, will have
already attempted (and failed) to open `/proc/{kpagecount,kpageflags}`, and
therefore they will keep failing to read them and report the correct results.

1. Should it be a responsibility of the user to instantiate anew the `PageMap`
to successfully read `/proc/{kpagecount,kpageflags}`?
2. Or should we check the capabilities on every read request to
`/proc/{kpagecount,kpageflags}`, and propagate any `EPERM` to the user?

In case (2), should `PageMap::pagemap(PID)` decouple reading
`/proc/PID/{maps,pagemap}` from reading `/proc/{kpagecount,kpageflags}`, so
that the former keeps succeeding (even when it can only return zeroed values)?
(This is what Linux chooses to happen anyway). Or would that be pointless
anyway, hence we should keep it as it is now?

- [] Workspaces

Split into 2 workspaces:

1. a lib crate that exposes all of the functionality;
2. a simple cli tool (i.e., bin crate) that uses the above.

- [ ] Convenience/Extra Functionality

- `pub fn pagemap(pid: u64) -> PageMapData`

- `pub fn uss(pid: u64) -> ..?..`
