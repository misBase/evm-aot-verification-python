ISABELLE ?= isabelle
DEFAULT_FILE ?= $(CURDIR)/EVM_SMT_Certificates.thy

.PHONY: open build
open:
	"$(ISABELLE)" jedit -d . -l EVM_SMT_Base "$(DEFAULT_FILE)"

build:
	"$(ISABELLE)" build -D .
