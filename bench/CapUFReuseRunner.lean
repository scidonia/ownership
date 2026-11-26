import Cap.UFReuseRunner

/-!
Executable controls for the state-threaded reusable union-find runner.

The proof module `Cap.UFReuseRunner` defines a private-constructor runner whose
`find` returns the root together with the successor runner. These guards compile
the same definitions and check the arrays and recorded histories the example
names:

* the starting runner's array is `[0,0,1,2,2]`;
* the first find from node `3` returns root `0`, and its successor's array is
  `[0,0,0,0,2]` with the single recorded path `[3,2,1]`;
* the second find, run on that successor from node `4`, returns root `0` and
  `[0,0,0,0,0]`, with both paths recorded;
* a fresh find from node `4` on the origin records the longer path `[4,2,1]`
  and leaves node `3` pointing at `2`, so its final array is `[0,0,0,2,0]`:
  the two-step result is not the fresh run.
-/

open Cap

#guard (Cap.reuseRunnerStart.parent == Cap.reuseStart)
#guard (Cap.reuseFirst == [0, 0, 0, 0, 2])

#guard ((Cap.PathRunner.find Cap.reuseRunnerStart 3 (by decide)).1 == 0)
#guard (Cap.reuseRunnerFirst.parent == [0, 0, 0, 0, 2])
#guard (Cap.reuseRunnerFirst.trace.map (fun c => c.path) == [[3, 2, 1]])

#guard ((Cap.PathRunner.find Cap.reuseRunnerFirst 4 (by decide)).1 == 0)
#guard (Cap.reuseRunnerSecond.parent == [0, 0, 0, 0, 0])
#guard (Cap.reuseRunnerSecond.trace.map (fun c => c.path) == [[3, 2, 1], [4, 2]])

#guard (Cap.reuseRunnerFreshFour.parent == [0, 0, 0, 2, 0])
#guard (Cap.reuseRunnerFreshFour.trace.map (fun c => c.path) == [[4, 2, 1]])
