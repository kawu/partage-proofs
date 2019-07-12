# Editing

Use `coq-custom.sh FILE.v`. The script should be in `~/.local/bin` and should
contain something similar to:

    coqide -async-proofs off -async-proofs-command-error-resilience off $1


# Compiling

Subsequent *.v files rely on the preceding ones.  To make the makefile:

    ./make_makefile.sh

To compile a specific file, e.g., `Basics.v` to `Basics.vo`:

    make Basics.vo

To compile all .v files to .vo:

    make
