module lesdump

go 1.26

require les v0.0.0

// The pinned upstream checkout is created by scripts/bootstrap.sh; it is never modified.
replace les => ../.work/upstream-les
