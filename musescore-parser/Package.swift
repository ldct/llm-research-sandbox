// swift-tools-version: 6.1
import PackageDescription

let package = Package(
    name: "MuseScoreParser",
    products: [
        .library(name: "MuseScoreParser", targets: ["MuseScoreParser"]),
    ],
    dependencies: [
        .package(url: "https://github.com/weichsel/ZIPFoundation.git", from: "0.9.19"),
    ],
    targets: [
        .target(
            name: "MuseScoreParser",
            dependencies: ["ZIPFoundation"]
        ),
        .executableTarget(
            name: "MuseScoreParserDemo",
            dependencies: ["MuseScoreParser"],
            path: "Sources/Demo"
        ),
        .testTarget(
            name: "MuseScoreParserTests",
            dependencies: ["MuseScoreParser"],
            resources: [.copy("Resources")]
        ),
    ]
)
