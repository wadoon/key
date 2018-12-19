import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;


public class Fooling {

	public static void main(String[] args) {
//		Runtime rt = Runtime.getRuntime();
//		try {
//			Process pr = rt.exec("\"D://Program Files (x86)//SageMath 8.4//runtime//bin//mintty.exe\" /bin/bash --login -c '/opt/sagemath-8.4/sage'");
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		final String generatedFolderName = "generated";
		final String generatedFileName = "gen.java";
		Path currentPath = Paths.get(System.getProperty("user.dir"));
		Path filePath = Paths.get(currentPath.toString(), generatedFolderName, generatedFileName);
		System.out.println(filePath.toString());
	}

}
