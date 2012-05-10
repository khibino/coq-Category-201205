
srcs = \
	Rel.v \
	Sets.v

objs  = $(srcs:.v=.vo)
globs = $(objs:.vo=.glob)

libdir = megacz-coq-categories

%.vo: %.v build_lib
	coqc $<

all: $(objs)

checkout_lib:
	[ -d $(libdir) ] || git clone http://git.megacz.com/coq-categories.git $(libdir)

build_lib: checkout_lib
	make -C $(libdir)

clean:
	rm -f $(objs)
	rm -f $(globs)