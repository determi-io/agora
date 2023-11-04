
# Agora: agda core library for determi

We migrate the code from the [hata project](https://github.com/project-hata/hata) to this library.

### Migration notes

The following changes are to be followed:
 - Move `Agora. to `Agora`
 - Merge `Agora.Set` with `Agora.Data.Universe` into `Agora.Data.Universe`


### Notes on conventions

Special cases where conventions are broken:
 - Setoids are defined under `Agora.Conventions.`, because they are required very early on.
   Following conventions they should have been defined in `Agora.Setoid.Definition`.


