package mutual_recursive;

public class Test01 {

	public void a(int x) {
		if (x>0) {
			b(x);
		} else {
			b(-x);
		}
		
	}

	private void b(int y) {
		if (y%2==0) {
			System.out.println("x");
			a(y-1);
		}
	}

	
}
