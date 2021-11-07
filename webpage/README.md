# Make `tutorial.v` into a webpage

``` sh
./dependencies.sh
```
For `coq-serapi` via `opam` and `alectryon` via `pip`. 

``` sh
make
```
Runs the file generation.

``` sh
make open
```
Will run the file generation and (assumes linux) `xdg-open` the `tutorial.html` interactive webpage with proof state in hover-over and click. 

``` sh
make clean
```
Will `rm` all web-related files.
