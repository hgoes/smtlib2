#!/bin/bash

BACKENDS="z3 mathsat pipe debug timing"
EXTRAS="emulated-modulus"
INSTALL="cabal install --disable-documentation --force-reinstalls"

$INSTALL

for b in $BACKENDS
do
    pushd backends/$b
    $INSTALL
    popd
done

for e in $EXTRAS
do
    pushd extras/$e
    $INSTALL
    popd
done
