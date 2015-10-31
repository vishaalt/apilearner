/**
 * 
 */
package exception_tests;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;

/**
 * @author schaef
 *
 */
public class DeclaredExceptionTest {

	public static final String filename = "./justatest.txt";

	public void mayThrow() throws IOException {
		BufferedReader rd = null;
		rd = new BufferedReader(new FileReader(new File(filename)));
		String inputLine = null;
		while ((inputLine = rd.readLine()) != null) {
			System.out.println(inputLine);
		}
		rd.close();
	}

	public void dummy() {
		System.err.println("not important");
	}
	
	public static void main(String[] args) {
		/*
		 * This test program is used to check if our graph handles declared exceptions properly. 
		 */
		DeclaredExceptionTest x = new DeclaredExceptionTest();
		try {
			x.mayThrow();
			x.dummy();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
