# cosbsides24
Colorado Springs BSides 2024 Type Theory

## To run demos / give this presentation:

* Install Docker (if you want to run Haskell/GHCI that way)
* Install coq
* Install Lean 4 VSCode plugin
* Install alire (Ada)
* Install VSCode marp plugin

## To generate presentation pdf:

```bash
docker run --rm --init -v $PWD:/home/marp/app/ -e LANG=$LANG -e MARP_USER="$(id -u):$(id -g)" marpteam/marp-cli presentation.md --pdf
```
