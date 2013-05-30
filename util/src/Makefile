# T.R.Marsh, Warwick.
#

# List of possible targets:
#
# make           -- builds class files
# make install   -- install a jar file of the classes
# make clean     -- cleans out the class files and other junk
# make dist      -- makes a tar file for distribution (me only)

DIST_DIR     = /tmp/$(PACKAGE)-$(VERSION) 

# PACKAGE      = name of package
# VERSION      = version number
# TOP_DIR      = path to top-level directory with generic Makefile.include
# BUILD_DIR    = where files generated during the build are stored
# PACKAGE_PATH = path to dig down to where classes are stored

PACKAGE      = util
VERSION      = 1.0.0
TOP_DIR      = ../..
BUILD_DIR    = ../build
PACKAGE_PATH = warwick/marsh/util

#
JAVA_PACKAGE_PATH = $(subst /,.,$(PACKAGE_PATH))

# include generic stuff
include $(TOP_DIR)/Makefile.include

JAR_FILE  = $(PACKAGE).jar

install:
	@echo "there is in fact no installation for util"

uninstall:
	@echo "there is in fact no installation/unistallation for util"

dist:
	mkdir -p    $(DIST_DIR) 
	cp -r src   $(DIST_DIR)
	cp README   $(DIST_DIR)
	cp Makefile $(DIST_DIR)
	cd $(DIST_DIR)/..; tar cvfz $(PACKAGE)-$(VERSION).tar.gz $(DIST_DIR); scp $(PACKAGE)-$(VERSION).tar.gz phsaap@sirius-b.csc.warwick.ac.uk:/data7/phsaap/software/.
	ssh phsaap@sirius-b.csc.warwick.ac.uk "cd /data7/phsaap/software ; ln -sf $(PACKAGE)-$(VERSION).tar.gz $(PACKAGE).tar.gz"



