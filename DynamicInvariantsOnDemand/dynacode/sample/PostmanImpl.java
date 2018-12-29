package sample;

import java.io.*;
import core.TraceMethodReturnObject;

public class PostmanImpl implements Postman {

	private PrintStream output;
	
	public PostmanImpl() {
		output = System.out;
	}
	
//	public PostmanImpl() throws IOException {
//		output = new PrintStream(new FileOutputStream("msg.txt"));
//	}
//
	public TraceMethodReturnObject deliverMessage(String msg) {
		output.println("[Postman] " + msg);
		output.flush();
		return new TraceMethodReturnObject();
	}
}
