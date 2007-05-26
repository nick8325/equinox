MTL       = ../minisat/mtl
MINISAT   = ../minisat/current-base
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h)
CFLAGS    = -I$(MTL) -I$(MINISAT) -Wall $(EXTRACFLAGS)

.PHONY:	all

all:	lib

include $(MTL)/template.mk
