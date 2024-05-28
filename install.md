# Installing and building the PERPL compiler

## Install

If you are using Windows, [install WSL (Windows Subsystem for Linux)](https://learn.microsoft.com/en-us/windows/wsl/install) if you don't have it already. 

Install Python 3, Git, and GHC if you don't have them already.

    sudo apt-get install python3 python3-pip git ghc

## Download

Download the [FGGs library](https://github.com/diprism/fggs), which is
the backend for PERPL. (`pip install fggs` works but currently doesn't
install the command-line tools we will be using.)

    git clone https://github.com/diprism/fggs

Download the source for the PERPL compiler:

    git clone https://github.com/diprism/perpl

## Build

Go to the directory where the compiler source code was downloaded:

    cd perpl

Build the compiler:

    make

