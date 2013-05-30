# To install, define the environment variable TRM_JAVA to point at\

# the directory you wish to install under then type make and, if\

# it works, make install.\

\

SUBDIRS = util ultracam usdriver#
# Generic part of Makefile to be included in the distribution Makefile
# for multi-component packages
#
# T.R.Marsh 10/11/06

.PHONY: all install clean uninstall

all:
	@@for p in $(SUBDIRS); do \
		echo '----- running "make all" for ' $$p; \
		make -C ./$$p/src --no-print-directory || exit 1; \
	done

install:
	@@for p in $(SUBDIRS); do \
		echo '----- running "make install" for ' $$p; \
		make -C ./$$p/src --no-print-directory  install || exit 1; \
	done

uninstall:
	@@for p in $(SUBDIRS); do \
		echo '----- running "make uninstall" for ' $$p; \
		make -C ./$$p/src --no-print-directory  uninstall || exit 1;; \
	done

clean:
	@@for p in $(SUBDIRS); do \
		echo '----- running "make clean" for ' $$p; \
		make -C ./$$p/src --no-print-directory clean || exit 1;\
	done
