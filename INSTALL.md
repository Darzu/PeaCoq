OS Specific Installation Instructions:
=========================
OSX:
----
Use brew to install ghc, cabal-install and campl4.
Use the dmg image from [the Coq page](https://coq.inria.fr/coq-84) to install Coq 8.4.
Put the coqtop utility on your PATH.
Make sure you're on our branch:
```git checkout peacoq-2014
cabal update
./setup.sh
cabal install```
and start the editor with
```./peacoq -p <PORT>```

ArchLinux:
----------
Assuming you are in this directory
```sudo pacman -S nodejs npm ghc ocaml alex happy haddock cabal-install
mkdir ./dependencybuilds
cd ./dependencybuilds
git clone https://aur.archlinux.org/camlp5-transitional.git
cd camlp5-transitional
makepkg -sri
cd ../
git clone https://aur.archlinux.org/coq.git
cd coq
git checkout aa60c4ba
makepkg -sri
cd ../../PeaCoq
cabal update
./setup.sh
cabal install```
The makepkg commands may take a while to run, and will at some point prompt you for your password. If you fail to respond it will time out. You can re-run just that command to get back to the password prompt quickly and then move on
You can then run peacoq with
```peacoq -p <PORT>```
peacoq will install to your cabal binaries folder, which may not be on your path, so for example, you may need to run
```~/.cabal/bin/peacoq -p <PORT>```
or the equivalent for your system.