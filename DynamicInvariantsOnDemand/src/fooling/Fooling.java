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
		System.out.println(System.getenv("SAGE_PATH"));
		
//		Runtime rt = Runtime.getRuntime();
//		try {
////			ProcessBuilder builder = new ProcessBuilder("D:\\Program Files (x86)\\SageMath 8.4\\runtime\\bin\\mintty.exe", "/bin/bash --login -c '/opt/sagemath-8.4/sage /home/sage/test.sage'");
////			ProcessBuilder builder = new ProcessBuilder("D:\\Program Files (x86)\\SageMath 8.4\\runtime\\bin\\mintty.exe", "/bin/bash", "-s");
//			ProcessBuilder builder = new ProcessBuilder("sage", "-python", "/home/daniel/git/dig/dig/dig.py", "/home/daniel/git/dig/traces/NLA/tcs/cohendiv.l1a.tcs");
////			ProcessBuilder builder = new ProcessBuilder("D:\\Program Files (x86)\\SageMath 8.4\\runtime\\bin\\mintty.exe", "/bin/bash", "--login", "-c", "/opt/sagemath-8.4/sage /home/sage/test.sage");
////			ProcessBuilder builder = new ProcessBuilder("D:\\Program Files (x86)\\SageMath 8.4\\runtime\\bin\\mintty.exe", "/bin/bash", "--login", "-c", "/opt/sagemath-8.4/sage /home/sage/test.sage", ">", "test.txt");
////			ProcessBuilder builder = new ProcessBuilder("D:\\Program Files (x86)\\SageMath 8.4\\runtime\\bin\\mintty.exe");
////			Process pr = rt.exec("\"D:\\Program Files (x86)\\SageMath 8.4\\runtime\\bin\\mintty.exe\" /bin/bash --login -c '/opt/sagemath-8.4/sage /home/sage/test.sage' > /home/sage/test.txt");
//			builder.redirectErrorStream(true);
////			File output = new File("C:\\Users\\Daniel\\test.txt");
////			builder.redirectOutput(output);
////			builder.redirectOutput(Redirect.INHERIT);
//			Process p = builder.start();
////			int result = p.waitFor();
//			
//			
////			PrintStream toP = new PrintStream(p.getOutputStream());
//			BufferedWriter toP = new BufferedWriter(new OutputStreamWriter(p.getOutputStream()));
//			BufferedReader fromP = new BufferedReader(new InputStreamReader(p.getInputStream()));
//			
//			
////		    toP.write("/bin/bash --login -c '/opt/sagemath-8.4/sage /home/sage/test.sage'"+"\n");
////		    toP.write("ls -la" + "\n");
//			//toP.write("'/opt/sagemath-8.4/sage /home/sage/test.sage'" + "\n");
//		    
//		    //toP.flush();
////		    toP.close();
////		    //System.err.println("stdin: \""+line+"\"");
//		    while(!fromP.ready());                            // sed hangs, cat doesn't
//		    
//		    //System.out.println("result: \""+fromP.readLine()+"\"");
//		    String line;
//		    String lastLine = null;
//		    while((line = fromP.readLine()) != null){
//		        System.out.println(line);
//		        lastLine = line;
//		    }
//		    
//		    System.out.println("Invs: " + lastLine);
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//		final String generatedFolderName = "generated";
//		final String generatedFileName = "gen.java";
//		Path currentPath = Paths.get(System.getProperty("user.dir"));
//		Path filePath = Paths.get(currentPath.toString(), generatedFolderName, generatedFileName);
		
////		System.out.println(filePath.toString());
//		
//		 File file = new File("C:\\BachelorEclipse\\Tools\\z3-4.8.4\\bin\\z3.exe");
//		 if (file.exists()) {
//			 System.out.println("exists");
//		 } else
//			 System.out.println("not exists");
	}
}
