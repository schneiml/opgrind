Opgrind
=======

A simple Valgrind plugin to do instruction counting.

It tries to be fairly fast (faster than `memcheck` or `lackey` (also shipped with Valgrind)), but it is still slow, due to how Valgrind works. Actually, Valgrind is not really the right tool for the job, but unlike e.g. `perf_events` it works even on locked-down shared systems or virtual machines.

The counts reported are actual instructions (_guest instructions_ in valgrind terms), but based on IR instructions. So a machine instruction can be listed as mem, FP, and int (or similar) at the same time (actually this is very common). The instruction classifications are very vague and potentially incorrect, the most useful ones are probably those related to SSE/AVX. 

Install
-------

Get the Valgrind source code and put this `opgrind` folder into the source root. Follow Section 2.2.3 in the Valgrind Technical Documentation to set up automake to build the new tool, then compile and install (potentially with a  `--prefix` in your home).

For CMSSW users, make sure that `VALGRIND_LIB` points to your install.

Usage
-----

`valgrind --tool=opgrind <program>`
