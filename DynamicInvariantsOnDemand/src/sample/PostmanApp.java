package sample;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;

import core.TraceMethodReturnObject;
import dynacode.DynaCode;

public class PostmanApp {

	public static void main(String[] args) throws Exception {
		BufferedReader sysin = new BufferedReader(new InputStreamReader(System.in));

		Postman postman = getPostman();

		while (true) {
			System.out.print("Enter a message: ");
			String msg = sysin.readLine();

			TraceMethodReturnObject o = postman.deliverMessage(msg);
			System.out.println("o");
		}
	}

	private static Postman getPostman() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (Postman) dynacode.newProxyInstance(Postman.class,
				"sample.PostmanImpl");
	}

}
