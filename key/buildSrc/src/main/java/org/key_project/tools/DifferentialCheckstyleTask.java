package org.key_project.tools;

import org.codehaus.groovy.runtime.ProcessGroovyMethods;
import org.gradle.api.DefaultTask;
import org.gradle.api.file.SourceDirectorySet;
import org.gradle.api.tasks.InputFile;
import org.gradle.api.tasks.InputFiles;
import org.gradle.api.tasks.OutputFile;
import org.gradle.api.tasks.TaskAction;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Set;


//https://guides.gradle.org/writing-gradle-plugins/

public class DifferentialCheckstyleTask /*extends JavaExec*/ extends DefaultTask {
    @InputFile
    public File checkConfig = new File("key_checks.xml");

    @InputFiles
    //public SourceDirectorySet sourceDirectorySet;
    public Set<File> sourceDirectories;

    @OutputFile
    public File diffFile;

    @OutputFile
    public File report = new File(getProject().getBuildDir(), "reports/diffcheck/report.txt");


    @TaskAction
    public void runFirst() {
        diffFile.getParentFile().mkdirs();
        System.out.format("write to diffFile: %s%n", diffFile.getAbsolutePath());
        System.out.format("rules: %s%n", checkConfig.getAbsolutePath());

        try {
            Process p = ProcessGroovyMethods.execute("git merge-base HEAD origin/master");
            p.waitFor();
            String mergeBase = new BufferedReader(new InputStreamReader(p.getInputStream())).readLine();
            System.out.println(mergeBase);
            ProcessGroovyMethods.execute(
                    String.format("git diff - U0 %s > %s", mergeBase, diffFile));
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
        //String mergeBase = "git merge-base HEAD origin/master".execute().text.trim();
        //"git diff - U0 $mergeBase > $diffFile".execute();
    }


    @TaskAction
    public void run() {
        try {
            String cacheFile = getProject().relativeProjectPath("build/tmp/checkstyle.cache");
            com.puppycrawl.tools.checkstyle.Main.main(
                    //http://checkstyle.sourceforge.net/config_reporting.html#Caching_Support
                    "-Dcheckstyle.cache.file=" + cacheFile,
                    "-o", report.getAbsolutePath(),
                    "-c", checkConfig.getAbsolutePath(),
                    sourceDirectories.iterator().next().getAbsolutePath()//try first one, just for testing
            );
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @TaskAction
    public void runLast() {
        //sed - e 's/<!--KeY\(.*\)-->/\1/' key_checks.xml > key_checks_incremental.xml
    }
}

