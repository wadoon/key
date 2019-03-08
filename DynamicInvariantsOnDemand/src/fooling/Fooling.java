package fooling;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.lang.ProcessBuilder.Redirect;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Scanner;

import de.uka.ilkd.key.logic.TermBuilder;

public class Fooling {

	public static void main(String[] args) throws InterruptedException {
		Cohen c = new Cohen();
		int res = c.cohenDivide(19, 3);
		System.out.println(res);
	}
}
