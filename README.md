Simple implementation of a call graph construction. Nothing smart happening yet.

run with 
	
	./gradlew jar
	cd build/libs/
	java -jar apilearner.jar -j ../classes/main

and you get a file *out.dot* containing a kind-of call graph of the project itself. Call

	dot -Tpdf out.dot -o out.pdf

to get a pdf version.