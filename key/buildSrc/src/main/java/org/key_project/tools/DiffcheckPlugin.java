package org.key_project.tools;

import org.gradle.api.Action;
import org.gradle.api.Plugin;
import org.gradle.api.Project;
import org.gradle.api.plugins.JavaPluginConvention;
import org.gradle.api.tasks.SourceSet;

import java.io.File;

public class DiffcheckPlugin implements Plugin<Project> {
    //Inspiration in https://github.com/gradle/gradle/blob/master/subprojects/antlr/src/main/java/org/gradle/api/plugins/antlr/AntlrPlugin.java
    @Override
    public void apply(Project project) {
        SourceSet ssMain = project.getConvention().getPlugin(JavaPluginConvention.class).getSourceSets().getByName("main");
        project.getTasks().register("diffCheck", DifferentialCheckstyleTask.class, new Action<DifferentialCheckstyleTask>() {
            @Override
            public void execute(DifferentialCheckstyleTask task) {
                task.setGroup("verification");
                task.diffFile = new File(project.getRootDir(), "build/tmp/checkstyle-diff.txt");
                task.checkConfig = new File(project.getRootDir(), "scripts/tools/checkstyle/key_checks.xml");
                task.setDescription("Processes the " + ssMain.getName() + " Antlr grammars.");
                task.sourceDirectories = ssMain.getJava().getSrcDirs();//ssMain.getAllJava();
            }
        });
    }
}
