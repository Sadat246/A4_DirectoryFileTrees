#--------------------------------------------------------------------
# Makefile for Assignment 4, Part 3
# Builds the ft executable
#--------------------------------------------------------------------

CC     = gcc217
CFLAGS = -g

all: ft

clean:
	rm -f *.o ft

clobber: clean
	rm -f *~

ft: ft.o nodeFT.o dynarray.o path.o ft_client.o
	$(CC) $(CFLAGS) ft.o nodeFT.o dynarray.o path.o ft_client.o -o ft

ft.o: ft.c ft.h nodeFT.h a4def.h dynarray.h path.h
	$(CC) $(CFLAGS) -c ft.c

nodeFT.o: nodeFT.c nodeFT.h ft.h a4def.h dynarray.h path.h
	$(CC) $(CFLAGS) -c nodeFT.c

dynarray.o: dynarray.c dynarray.h
	$(CC) $(CFLAGS) -c dynarray.c

path.o: path.c path.h a4def.h
	$(CC) $(CFLAGS) -c path.c

ft_client.o: ft_client.c ft.h a4def.h
	$(CC) $(CFLAGS) -c ft_client.c


