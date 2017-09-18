# A small implementation of NFS

## Aim of the project

This small implementation of the number field sieve algorithm to compute
discrete logarithms in prime fields proposes a very simple implementation of
the four main different steps of NFS.

Details of this implementation are described in Laurent Grémy's thesis.

## How to use

With [Sage](http://www.sagemath.org/) 8.0, simply launch ```sage
smallnfs.sage```. It will compute an individual logarithm in
GF(6283185307179586476925547). You can easily modify the parameters by
modifying the lines after ```Data```.

## Limitation

The last step, the computation of an individual logarithm, does not compute for
now the logarithm of a large target.

## Licence

This project is distributed under the [Creative Commons Zero license](LICENSE).
