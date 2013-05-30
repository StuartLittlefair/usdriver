# T.R.Marsh, Warwick.

# List of possible targets:
#
# make           -- builds class files
# make clean     -- cleans out the class files and other junk
# make dist      -- makes a tar file for distribution (me only)
# make uninstall -- removes installed software

# PACKAGE      = name of package
# MAIN         = name of program
# VERSION      = version number
# TOP_DIR      = path to top-level directory with generic Makefile.include
# BUILD_DIR    = where files generated during the build are stored
# PACKAGE_PATH = path to dig down to where classes are stored

PACKAGE      = ultracam
VERSION      = 1.0.0
TOP_DIR      = ../..
BUILD_DIR    = ../build
PACKAGE_PATH = warwick/marsh/ultracam

DIST_DIR            = /tmp/$(PACKAGE)-$(VERSION)

JAVA_PACKAGE_PATH   = $(subst /,.,$(PACKAGE_PATH))

JAR_FILE     = $(PACKAGE).jar

FILES        = TreeDomNode.java

# include generic stuff
include $(TOP_DIR)/Makefile.include

install:
	@echo "there is in fact no installation for ultracam"

uninstall:
	@echo "there is in fact no installation/unistallation for ultracam"

dist:
	mkdir -p    $(DIST_DIR)
	cp -r src   $(DIST_DIR)
	cp README   $(DIST_DIR)
	cp Makefile $(DIST_DIR)
	cd $(DIST_DIR)/..; tar cvfz $(PACKAGE)-$(VERSION).tar.gz $(DIST_DIR); scp $(PACKAGE)-$(VERSION).tar.gz phsaap@sirius-b.csc.warwick.ac.uk:/data7/phsaap/software/.
	ssh phsaap@sirius-b.csc.warwick.ac.uk "cd /data7/phsaap/software ; ln -sf $(PACKAGE)-$(VERSION).tar.gz $(PACKAGE).tar.gz"




