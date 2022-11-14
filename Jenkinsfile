pipeline {
    agent {
        docker {
            label "bwcloud"
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
                sh 'echo test'
            }
        }

        stage('Test: testProveRules') {
            steps {
                sh 'echo test'
            }            }
        }

        stage('Test: testRunAllFunProofs') {
            steps {
                sh 'echo test'
            }
            }
        }

        stage('Test: testRunAllInfProofs') {
            steps {
                sh 'echo test'
            }
            }
        }

        stage('Test: Optional Features') {
            steps {
                catchError(buildResult: 'SUCCESS', stageResult: 'FAILURE') {
                   sh 'echo test'
            }
                }
            }
        }

        stage('Check Formatting') {
            steps {
                catchError(buildResult: 'SUCCESS', stageResult: 'FAILURE') {
                    sh 'echo test'
            
                }
            }
        }

        stage('Docs') {
            steps{ sh 'key/scripts/jenkins/generateDoc.sh'}
        }
    }

    post {
        always {
            junit(testResults: 'key/*/build/test-results/*/*.xml', allowEmptyResults: true, healthScaleFactor: 1)
        }
    }
}
