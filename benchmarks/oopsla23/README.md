### Benchmarks for "Exact Recursive Probabilistic Programming", OOPSLA 2023
This directory contains the code for running the benchmarks used to create Figures 6 and 7 in the paper.

Since there are so many dependencies, we recommend using the Docker image available at [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.7510763.svg)](https://doi.org/10.5281/zenodo.7510763).

## Dependencies
If you want to run everything locally, you will need to make sure the following are installed, and all of their dependencies:
- Clone https://github.com/diprism/fggs into the main PERPL directory (here/../../)
- [WebPPL](http://webppl.org/)
- [Dice](http://dicelang.cs.ucla.edu/about/) (local install)
- [Hyperfine](https://github.com/sharkdp/hyperfine)
- Perl and the packages: `JSON` `Text::CSV`
- `ghc`
- `pdflatex` (via `texlive`)
- Python 3 and the packages: `torch` `pydot` `torch-semiring-einsum` `tqdm` `mypy` `numpy`

Make sure `dice`, `webppl`, `perl`, `hyperfine`, `runhaskell`, and `pdflatex` are in your `PATH`.

## Running the benchmarks
Now that all dependencies are installed, you can simply run
```bash
./bench.sh
```
to run the entire benchmarks, generating `plots_6_7.pdf`.

This may take the better part of a day to run, so if you want faster results, decrease the parameter `hyperfine_runs` in `bench.sh`. That changes how many times Hyperfine runs each program before averaging their runtimes. By default, it is set to 10; however, if even set to 1 it anecdotally seems to produce mostly similar results to the paper's while significantly reducing the time it takes to run the benchmarks.