#! /bin/bash

FILE="$1"

[ -e "$FILE" ] || exit 1

LST="$(cat "$FILE" | cut -d' ' -f1 | sort | uniq)"

(for KEY in $LST; do LINES=`grep -c $KEY "$FILE"`; LINE=$(($LINES / 3 + 1)); echo "$LINE/$LINES" >&2; REPTIME=`grep $KEY "$FILE" | cut -d' ' -f 3 | sort -n | head -n $LINE | tail -1`; grep "$KEY time: $REPTIME" "$FILE"; done) | sort
