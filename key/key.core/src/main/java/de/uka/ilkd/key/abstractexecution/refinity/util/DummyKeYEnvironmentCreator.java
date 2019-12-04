// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.util;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * @author Dominic Steinhoefel
 */
public class DummyKeYEnvironmentCreator {
    private Services services = null;
    private KeYJavaType kjt = null;

    public void initialize() throws ProblemLoaderException, IOException {
        KeYEnvironment<?> environment = null;
        final Path tmpDirPath = Files.createTempDirectory("REFINITY_Init_");
        final Path tmpSrcPath = Files.createDirectory(tmpDirPath.resolve("dummyPackage"));
        final Path tmpKeYFile = Files.createFile(tmpDirPath.resolve("dummy.key"));
        final Path tmpJavaFile = Files.createFile(tmpSrcPath.resolve("DummyClass.java"));

        Files.write(tmpKeYFile, ("\\profile \"Java Profile\";\n" + //
                "\\javaSource \"dummyPackage\";\n" + //
                "\\problem {true}").getBytes());
        Files.write(tmpJavaFile, ("package dummyPackage;\n" + //
                "public class DummyClass {}").getBytes());

        environment = KeYEnvironment.load( //
                JavaProfile.getDefaultInstance(), tmpKeYFile.toFile(), null, null, null, true);

        this.services = environment.getLoadedProof().getServices();
        this.kjt = this.services.getJavaInfo().getKeYJavaType("dummyPackage.DummyClass");
    }

    public Optional<Services> getDummyServices() {
        return Optional.ofNullable(services);
    }

    public Optional<KeYJavaType> getDummyKjt() {
        return Optional.ofNullable(kjt);
    }
}
