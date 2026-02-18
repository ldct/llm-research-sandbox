plugins {
    java
    application
}

repositories {
    mavenCentral()
}

dependencies {
    implementation("io.projectreactor:reactor-core:3.6.0")
}

application {
    mainClass.set("ReactorDemo")
}
