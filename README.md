## What is it?
A repo for tracking my exercises for https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2023_SS/index.html

## What is cool thing about it?
Rather than opam's intermediate feature for managing localized development environment, in this repo, leveraging [esy](https://esy.sh/en/)'s feature.

Thanks to [WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq) project, from which I inspired a lot to make current project structure.

## How to build localized environment?

``` sh
esy shell
```
should set up all the necessary tooling for a sanitized environment.

## Caveat
Now you can remove all the installations from opam, especially, can remove opam switches. However, [tuareg](https://github.com/ocaml/tuareg) requires at least one opam switch exists, so you can do the following trick to pacify it:

``` sh
opam switch create default --empty
```
