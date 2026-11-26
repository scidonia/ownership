import Cap.UFReuse

/-!
Executable controls for the two-find reuse example.

The proof module `Cap.UFReuse` states and proves the exact post-states and the
ranked-forest witness that admits the second operation. These guards compile the
same definitions and check the arrays the example names, so the module is
elaborated as part of the capability controls as well as the library build:

* the first full-path compression of `[0,0,1,2,2]` from node `3` is
  `[0,0,0,0,2]`;
* the second full-path compression, run on that output from node `4`, is
  `[0,0,0,0,0]`.
-/

open Cap

#guard (Cap.reuseStart == [0, 0, 1, 2, 2])
#guard (Cap.reuseFirstPath == [3, 2, 1])
#guard (Cap.reuseFirstRoot == 0)
#guard (Cap.reuseFirst == [0, 0, 0, 0, 2])
#guard (Cap.reuseSecondPath == [4, 2])
#guard (Cap.reuseSecondRoot == 0)
#guard (Cap.reuseSecond == [0, 0, 0, 0, 0])
#guard (Cap.reuseTwoFinds == [0, 0, 0, 0, 0])
