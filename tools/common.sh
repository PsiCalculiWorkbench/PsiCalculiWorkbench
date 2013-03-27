
# currently only PolyML
SML_QUITE_OUTPUT="PolyML.print_depth 0;"
SML_NORMAL_OUTPUT="PolyML.print_depth 10;"

SML_OPTS=-q


CC=gcc
LDFLAGS="-L/opt/local/lib -lpolyml -lpolymain -Wl,-no_pie"
CFLAGS=
