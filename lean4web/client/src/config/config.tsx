import { LeanWebConfig } from './docs' // look here for documentation of the individual config options

const lean4webConfig: LeanWebConfig = {
  projects: [
    { folder: 'Lean4270', name: 'Lean 4.24.0' },
    { folder: 'Stable', name: 'Stable Lean 4.24.0' },
  ],
  serverCountry: null,
  contactDetails: null,
  impressum: null,
}

export default lean4webConfig
