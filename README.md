PeaCoq
======

PeaCrow is an augmented version of [the PeaCoq editor](http://goto.ucsd.edu/peacoq). As the user works through a Coq proof, PeaCrow tries to synthesize a series of tactics that can discharge any pending goals. 

To use PeaCrow, load one of the benchmarks and begin stepping through a proof by clicking Next. You can view all pending goals by clicking on the Goals tab. As PeaCrow finds solutions to pending goals, a count of available solutions will appear on the tab text. You can import a solution by opening the Goals tab and clicking on the solution text. You can also import solutions as autocomplete hints by pressing ctrl-space at any time when the editor pane is focused.

Our report, presentation slide, and benchmarks are all available in the peacrow folder.

Our code contributions are largely in [../web/src/brute.js] and [../web/src/goals.js].

Building PeaCoq/PeaCrow
-----------------------

To build our version of PeaCoq, first ensure you have a recent
[GHC](https://www.haskell.org/downloads) (at least 7.10), and
[Coq 8.4](https://coq.inria.fr/download). **Make sure you use Coq 8.4** -- the most recent version will not work!
Ensure that `coqtop` is somewhere in your `PATH`.
You will also need `wget` to fetch
all the necessary JavaScript libraries.

Once all dependencies are satisfied,
the following sequence of commands should
download and build PeaCoq:
```
  $ git clone https://github.com/Darzu/PeaCoq.git
  $ cd PeaCoq
  $ ./setup.sh
  $ cabal install
```
More detailed installation instructions for OS X and Archlinux are available [here](../INSTALL.md).

Running PeaCoq
--------------

```
  peacoq -p <PORT>
```

Then open `http://localhost:<PORT>` to start using PeaCoq!

