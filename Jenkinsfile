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
            steps{
                sh 'javac -version'
                sh 'key/scripts/jenkins/startupClean.sh'
            }
        }

        stage('Compile') {
            steps { 
                sh 'cd key && ./gradlew --parallel clean compileTest :key.ui:shadowJar :key.ui:distZip'
            }
        }

        stage('Test: JUnit') {
            steps {
                sh 'cd key && ./gradlew --continue test'
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
                      [file: 'key/key.core.test/testresults/runallproofs/NumberTestFiles.properties', label: '']],
                      style: 'line', title: '1 Number of considered examples', useDescr: true,
                      yaxis: '# of key files'

                plot csvFileName: 'plot-4acea630-1baa-4f25-b8e4-3370d9950347.csv',
                     group: 'runAllProofs', numBuilds: '200',
                     propertiesSeries: [
                      [file: 'key/key.core.test/testresults/runallproofs/Total rule apps.sum.properties', label: ''],
                      [file: 'key/key.core.test/testresults/runallproofs/Nodes.sum.properties', label: '']],
                      style: 'line',
                      title: '2 Total number of rule apps',
                      useDescr: true, yaxis: '#rule apps'
            }
        }
    }

    post {
        always {
            junit(testResults: 'key/*/build/test-results/test/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
        }
    }
}
