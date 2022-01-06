#!groovy

pipeline {
    agent {
        docker {
            image 'wadoon/key-test-docker:jdk11'
        }
    }

    environment {
        GRADLE_OPTS = '-Dorg.gradle.daemon=false'
    }

    stages {
        stage('Clean') {
            steps {
                sh 'javac -version'
                sh 'key/scripts/jenkins/startupClean.sh'
            }
        }

        stage('Compile') {
            steps {
                sh 'cd key && ./gradlew --parallel clean compileTest :key.ui:shadowJar :key.ui:distZip'
            }
        }

        stage("Run Tests") {
            parallel {
                stage('Test: JUnit') {
                    steps {
                        sh 'echo 1'
                        //sh 'cd key && ./gradlew --continue test'
                    }
                }

                stage('Test: testProveRules') {
                    steps {
                        sh 'cd key && ./gradlew --continue testProveRules'
                    }
                }

                stage('Test: testRunAllProofs') {
                    steps {
                        sh 'cd key && ./gradlew --continue testRunAllProofs'

                        plot csvFileName: 'plot-4acea630-1baa-4f25-b8e4-3370d9950347.csv',
                                group: 'runAllProofs', numBuilds: '200',
                                propertiesSeries: [
                                        [file: 'key/key.core.test/testresults/runallproofs/NumberTestFiles.properties', label: 'NumberTestFiles']],
                                style: 'line', title: '1 Number of considered examples', useDescr: true,
                                yaxis: '# of key files'

                        plot csvFileName: 'plot-4acea630-1baa-4f25-b8e4-3370d9950347.csv',
                                group: 'runAllProofs', numBuilds: '200',
                                propertiesSeries: [
                                        [file: 'key/key.core.test/testresults/runallproofs/Total rule apps.sum.properties', label: 'Total rule apps.sum'],
                                        [file: 'key/key.core.test/testresults/runallproofs/Nodes.sum.properties', label: 'Nodes.sum']],
                                style: 'line',
                                title: '2 Total number of rule apps',
                                useDescr: true, yaxis: '#rule apps'


                        plot csvFileName: 'plot-4abbaea630-1bbb-4f25-b8e4-3370d9950347.csv',
                                group: 'runAllProofs', numBuilds: '200',
                                propertiesSeries: [
                                        [file: 'key/key.core.test/testresults/runallproofs/Overall time (ms).sum.properties', label: 'Overall time (ms).sum'],
                                        [file: 'key/key.core.test/testresults/runallproofs/Automode time (ms).sum.properties', label: 'Automode time (ms).sum']],
                                style: 'line',
                                title: '4 Overall time',
                                useDescr: true, yaxis: 'time in ms'


                        plot csvFileName: 'plot-4acea630-1bbb-4f25-b8e4-3370d9950347.csv',
                                group: 'runAllProofs', numBuilds: '200',
                                propertiesSeries: [
                                        [file: 'key/key.core.test/testresults/runallproofs/Time per step (ms).avg.properties', label: 'Time per step (ms).avg']],
                                style: 'line',
                                title: '6 Time per step',
                                useDescr: true, yaxis: 'time in ms'

                        plot csvFileName: 'plot-4aceaa242323423630-1bbb-4f25-b8e4-3370d9950347.csv',
                                group: 'runAllProofs', numBuilds: '200',
                                propertiesSeries: [
                                        [file: 'key/key.core.test/testresults/runallproofs/Total Runtime Memory (kB).avg.properties', label: 'Total Runtime Memory (kB).avg']],
                                style: 'line',
                                title: '7 avg. memory consumption (after proof finished and GC)',
                                useDescr: true, yaxis: 'kB'

                        plot csvFileName: 'plot-agafsdafsdaf-1bbb-4f25-b8e4-3370d9950347.csv',
                                group: 'runAllProofs', numBuilds: '200',
                                propertiesSeries: [
                                        [file: 'key/key.core.test/testresults/runallproofs/Total Runtime Memory (kB).avg.properties', label: 'Total Runtime Memory (kB).avg']],
                                style: 'line',
                                title: '7 avg. memory consumption (after proof finished and GC)',
                                useDescr: true, yaxis: 'kB'


                        plot csvFileName: 'plot-aac01643-4fe5-453d-9183-71fecf398579.csv',
                                csvSeries: [[displayTableFlag: true,
                                             exclusionValues: 'Time per step (ms),Overall time (ms),Total rule apps',
                                             file: 'key/key.core.test/testresults/runallproofs/runStatistics.csv',                                             inclusionFlag: 'INCLUDE_BY_STRING',
                                             url: '']],
                                numBuilds: 200,
                                group: 'runAllProofsDetails', style: 'bar'
                        plot csvFileName: 'plot-bbc01643-4fe5-453d-9183-71fecf398579.csv',
                                csvSeries: [[displayTableFlag: true,
                                             exclusionValues: 'Overall time (ms)',
                                             file: 'key/key.core.test/testresults/runallproofs/runStatistics.csv',
                                             inclusionFlag: 'INCLUDE_BY_STRING',
                                             url: '']],
                                numBuilds: 200,
                                group: 'runAllProofsDetails', style: 'bar'
                        plot csvFileName: 'plot-ccc01643-4fe5-453d-9183-71fecf398579.csv',
                                csvSeries: [[displayTableFlag: true,
                                             exclusionValues: 'Total rule apps',
                                             file: 'key/key.core.test/testresults/runallproofs/runStatistics.csv',                                             inclusionFlag: 'INCLUDE_BY_STRING',
                                             url: '']],
                                numBuilds: 200,
                                group: 'runAllProofsDetails', style: 'bar'
                    }
                }
            }
        }
    }

    post {
        always {
            junit(testResults: 'key/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
        }
    }
}
