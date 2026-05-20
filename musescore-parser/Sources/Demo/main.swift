import Foundation
import MuseScoreParser

func main() throws {
    let args = CommandLine.arguments
    guard args.count > 1 else {
        print("Usage: MuseScoreParserDemo <file.mscz|file.mscx>")
        print("")
        print("Parses a MuseScore file and prints its contents.")
        return
    }

    let path = args[1]
    let parser = MuseScoreParser()
    let file = try parser.parse(fileAt: path)

    print("═══════════════════════════════════════")
    print("MuseScore File Parser")
    print("═══════════════════════════════════════")
    print("Format version: \(file.formatVersion)")
    print("Title: \(file.score.title ?? "(none)")")
    print("Composer: \(file.score.composer ?? "(none)")")
    print("Division: \(file.score.division) ticks/quarter")
    print("")

    // Parts
    print("Parts (\(file.score.parts.count)):")
    for (i, part) in file.score.parts.enumerated() {
        print("  [\(i+1)] \(part.trackName) (\(part.instrument.longName))")
        print("       Instrument ID: \(part.instrument.id)")
        if let min = part.instrument.minPitch, let max = part.instrument.maxPitch {
            print("       Pitch range: \(min)-\(max)")
        }
    }
    print("")

    // Staves with measures
    print("Staves (\(file.score.staves.count)):")
    for staff in file.score.staves {
        print("\n─── Staff \(staff.id) ─── (\(staff.measures.count) measures)")

        for (mi, measure) in staff.measures.enumerated() {
            print("  Measure \(mi + 1):")
            for (vi, voice) in measure.voices.enumerated() {
                if measure.voices.count > 1 {
                    print("    Voice \(vi + 1):")
                }
                let indent = measure.voices.count > 1 ? "      " : "    "
                for element in voice {
                    switch element {
                    case .timeSig(let ts):
                        print("\(indent)Time: \(ts.numerator)/\(ts.denominator)")
                    case .keySig(let ks):
                        let desc = ks.accidental == 0 ? "C major/A minor" :
                            ks.accidental > 0 ? "\(ks.accidental) sharp(s)" : "\(abs(ks.accidental)) flat(s)"
                        print("\(indent)Key: \(desc)")
                    case .clef(let c):
                        print("\(indent)Clef: \(c.clefType)")
                    case .chord(let chord):
                        let noteStr = chord.notes.map { $0.noteName }.joined(separator: "+")
                        let durStr = chord.durationType.rawValue
                        let dotStr = chord.dots > 0 ? String(repeating: ".", count: chord.dots) : ""
                        print("\(indent)♪ \(noteStr) [\(durStr)\(dotStr)] (dur=\(chord.totalDuration)q)")
                    case .rest(let rest):
                        let durStr = rest.durationType.rawValue
                        let dotStr = rest.dots > 0 ? String(repeating: ".", count: rest.dots) : ""
                        print("\(indent)𝄾 rest [\(durStr)\(dotStr)] (dur=\(rest.totalDuration)q)")
                    case .barline(let bl):
                        print("\(indent)| \(bl.subtype)")
                    case .direction(let d):
                        print("\(indent)→ \(d.type)")
                    case .unknown(let tag):
                        print("\(indent)? <\(tag)>")
                    }
                }
            }
        }
    }

    // Summary stats
    print("\n═══════════════════════════════════════")
    let totalNotes = file.score.staves.flatMap { $0.measures }
        .flatMap { $0.voices }
        .flatMap { $0 }
        .compactMap { elem -> Int? in
            if case .chord(let c) = elem { return c.notes.count }
            return nil
        }
        .reduce(0, +)
    let totalMeasures = file.score.staves.first?.measures.count ?? 0
    print("Total measures: \(totalMeasures)")
    print("Total notes: \(totalNotes)")
    print("═══════════════════════════════════════")
}

try main()
