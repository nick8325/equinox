#!/bin/sh

N=0
while read PRE T
do
  echo "$PRE $T"
  if [ "$PRE" = "%%inj" ]
  then
    N=`expr $N + 1`
    T0=`echo "$T" | sed 's/,X//g' | sed 's/X,//g' | sed 's/(X)//'`
    A="a$N$T0"
    B="b$N$T0"
    INVTY=`echo "inv$N$T" | sed "s/X/Y/g"`
    echo "cnf(arg_$N,axiom, $A != $B)."
    TA=`echo "$T" | sed "s/X/$A/g"`
    TB=`echo "$T" | sed "s/X/$B/g"`
    TINVTY=`echo "$T" | sed "s/X/$INVTY/g"`
    echo "cnf(not_inj_or_surj_$N,axiom, ($TA = $TB | $TINVTY = Y))."
  elif [ "$PRE" = "%%surj" ]
  then
    N=`expr $N + 1`
    T0=`echo "$T" | sed 's/,X//g' | sed 's/X,//g' | sed 's/(X)//'`
    C="c$N$T0"
    TY=`echo "$T" | sed "s/X/Y/g"`
    INVT="inv$N$T"
    INVTTY=`echo "$INVT" | sed "s/X/$TY/g"`
    echo "cnf(inj_or_not_surj_$N,axiom, ($INVTTY = Y | $T != $C))."
  fi  
done

