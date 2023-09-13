import path from 'path';
import { fileURLToPath } from "url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

export default {
  entry: './src/Main.js',
  mode: 'development',
  output: {
    filename: 'logic-questions.min.js',
    path: path.resolve(__dirname, 'dist'),
    library: 'logicQuestions',
  },
};