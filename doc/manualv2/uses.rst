Uses: The Pwb Guerilla Module System
====================================

Pwb uses its own module system called Uses. This module system is preloaded
with the sml compiler wrapper:

::

    psi sml ...

And it is used by the ``psi load-instance`` when loading an instance.

The goal of this module system is to be unobtrusive and to be familiar to other
module systems found in standard programming languages, albeit we do not
attempt to implement any kind of namespace handling only the file loading. It
is compatible with the ``use`` function as long as the same files are not being
loaded by both systems. Every file in Pwb package uses this module system.

The Uses module system builds a dependency graph, thus it tries to load files
in the right order and only once without shadowing definitions.  Uses
identifies files not by their filesystem name, but by their canonical name
which depends on the file contents instead of the filepath (currently this is
an MD5 hash, but this is an implementation detail and might change in the
future). Furthermore, Uses is stateful, meaning that successive calls to
``Uses.uses`` won't load already loaded files.

Any SML file is regarded as a Uses module if it is on the Uses search path.
SML files can have any of ``.ML``, ``.sml`` extensions. The dependencies of a
module is defined at the beginning of a file as a comment, e.g.

::

    (* uses pwb/missing,
            pwb/parser
    *)

    signature SOME_SIG = sig ... end;

    ... some code ...

    structure SomeStruct : SOME_SIG = struct .. end;

    ... some code ...


This files depends on two modules ``pwb/missing`` and ``pwb/parser`` which can be
found on path ``$PWB_HOME_PATH`` as ``$PWB_HOME_PATH/pwb/missing.ML`` and
``$PWB_HOME_PATH/pwb/parser.ML``. Uses then preloads these files before loading
the above example file. While doing so Uses traverses ``pwb/parser`` and
``pwb/missing`` dependencies. The ``/`` in the module name is converted to the
actual directory separator on a specific platform.

To load one file, one can write at the beginning of the file

::

    (* uses pwb/missing *)

Sometimes it is convienient to load a file not on path, this can be done with
Uses by using local path module syntax

::

    (* uses @some/directory/file.ML *)

Note that this is a real file path, thus it is platform specific.

The command ``psi sml`` accepts module specifications. So the above example could
be loaded as

::

    psi sml pwb/missing pwb/parser @file.ML

The search path of Uses can be expanded with function

::

    Uses.prependToPath path
    Uses.appendToPath path


See ``$PWB_HOME_PATH/pwb/bootstrap/uses.ML`` for the implementation details.

