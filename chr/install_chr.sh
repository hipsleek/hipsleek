#!/bin/sh

#### swi-prolog has built-in support for CHR, so need not install anything else but prolog
sudo apt-get install software-properties-common
sudo apt-add-repository ppa:swi-prolog/stable
sudo apt-get update
sudo apt-get install swi-prolog
sudo cp --parents chr/session_orders.pl /usr/local/src
sudo chmod a+x /usr/local/src/chr/session_orders.pl
sudo rm /usr/local/bin/orderchr
sudo ln -s /usr/local/src/chr/session_orders.pl /usr/local/bin/orderchr

