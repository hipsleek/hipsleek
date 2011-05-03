#!/bin/bash

#check if logging is needed
logging=0
for i in "$@" ; do 
    if [[ "$i" =~ "log-" || "$i" =~ "dd" ]] ; then
        logging=1;
    fi;
done

PATH_TMP=`dirname $0`

if [ $logging == 1 ]; then
    #copy all log files to some temp files (in order to have name consistency with the config file)
    for FILE in allinput.* ; do
        file_tmp=$(echo $FILE | tr [.] '_')
        cp "$FILE" $file_tmp
    done

    #running command
    BOLT_FILE=$PATH_TMP"/config" $PATH_TMP"/EXECUTABLE_NAME" $@

    #replaces only the log files that gathered new information after this running session
    for FILE in allinput.* ; do
        if [ ! -s $FILE ] ; then
            file1=$(echo $FILE | tr [.] '_')
            cp $file1 "$FILE"
        fi ;
    done

    #remove temp files
    rm allinput_*
else
    #run hip without logging
    $PATH_TMP"/EXECUTABLE_NAME" $@
fi;
