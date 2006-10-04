MTL       = ../minisat/mtl
MINISAT   = ../minisat/current-base
#MINISAT   = ../minisat/stable-1.14
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h)
#CFLAGS    = -I$(MTL) -I$(MINISAT) -Wall -mno-cygwin
CFLAGS    = -I$(MTL) -I$(MINISAT) -Wall

.PHONY:	all

all:	lib

include $(MTL)/template.mk
