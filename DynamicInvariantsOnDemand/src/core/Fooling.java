package core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Scanner;


public class Fooling {

	public static void main(String[] args) {
		Runtime rt = Runtime.getRuntime();
		try {
			Process pr = rt.exec("\"D://Program Files (x86)//SageMath 8.4//runtime//bin//mintty.exe\" /bin/bash --login -c '/opt/sagemath-8.4/sage'");
	        OutputStream stdin = pr.getOutputStream(); // <- Eh?
	        InputStream stdout = pr.getInputStream();

	        BufferedReader reader = new BufferedReader(new InputStreamReader(stdout));
	        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(stdin));

	        writer.write("Sup buddy");
	        writer.flush();
	        writer.close();

	        Scanner scanner = new Scanner(stdout);
	        while (scanner.hasNextLine()) {
	            System.out.println(scanner.nextLine());
	        }
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
//		final String generatedFolderName = "generated";
//		final String generatedFileName = "gen.java";
//		Path currentPath = Paths.get(System.getProperty("user.dir"));
//		Path filePath = Paths.get(currentPath.toString(), generatedFolderName, generatedFileName);
//		System.out.println(filePath.toString());
	}

}
