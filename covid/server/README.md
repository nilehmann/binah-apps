# server

## Setup
You need to have stack in your `$PATH` for the following to work. If you want to edit `Model.binah` you'll also need [binah-codegen](https://github.com/nilehmann/binah-codegen) see below for further instructinos.

## Build the code

```
make build
```

## Run the server
The following will start the server in 127.0.0.0:3000

```
make run
```

## Note on editing `Model.binah`

If you edit `Model.binah` you'll first need to generate the corresponding `Model.hs`. The commands `make build` and `make run` are wrappers over `stack build` and `stack run` that auto generate `Model.hs` from `Model.binah` when necessary. For this to work you need to have `binah-codegen` in your `$PATH`. See https://github.com/nilehmann/binah-codegen for instructions. If you don't modify `Model.binah` things should work just fine because `Model.hs` is under version control.
