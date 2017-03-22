#!/bin/sh

# swi-prolog has built-in support for CHR, so need not install anything else but prolog
sudo apt-get install software-properties-common
sudo apt-add-repository ppa:swi-prolog/stable
sudo apt-get update
sudo apt-get install swi-prolog
