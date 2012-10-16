require 'psych/scalar_scanner'

unless defined?(Regexp::NOENCODING)
  Regexp::NOENCODING = 32
end

module Psych
  module Visitors
    ###
    # This class walks a YAML AST, converting each node to ruby
    class ToRuby < Psych::Visitors::Visitor
      def initialize ss = ScalarScanner.new
        super()
        @st = {}
        @ss = ss
        @domain_types = Psych.domain_types
      end

      def accept target
        result = super
        return result if @domain_types.empty? || !target.tag

        key = target.tag.sub(/^[!\/]*/, '').sub(/(,\d+)\//, '\1:')
        key = "tag:#{key}" unless key =~ /^(tag:|x-private)/

        if @domain_types.key? key
          value, block = @domain_types[key]
          return block.call value, result
        end

        result
      end

      def deserialize o
        if klass = Psych.load_tags[o.tag]
          instance = klass.allocate

          if instance.respond_to?(:init_with)
            coder = Psych::Coder.new(o.tag)
            coder.scalar = o.value
            instance.init_with coder
          end

          return instance
        end

        return o.value if o.quoted
        return @ss.tokenize(o.value) unless o.tag

        case o.tag
        when '!binary', 'tag:yaml.org,2002:binary'
          o.value.unpack('m').first
        when /^!(?:str|ruby\/string)(?::(.*))?/, 'tag:yaml.org,2002:str'
          klass = resolve_class($1)
          if klass
            klass.allocate.replace o.value
          else
            o.value
          end
        when '!ruby/object:BigDecimal'
          require 'bigdecimal'
          BigDecimal._load o.value
        when "!ruby/object:DateTime"
          require 'date'
          @ss.parse_time(o.value).to_datetime
        when "!ruby/object:Complex"
          Complex(o.value)
        when "!ruby/object:Rational"
          Rational(o.value)
        when "!ruby/class", "!ruby/module"
          resolve_class o.value
        when "tag:yaml.org,2002:float", "!float"
          Float(@ss.tokenize(o.value))
        when "!ruby/regexp"
          o.value =~ /^\/(.*)\/([mixn]*)$/
          source  = $1
          options = 0
          lang    = nil
          ($2 || '').split('').each do |option|
            case option
            when 'x' then options |= Regexp::EXTENDED
            when 'i' then options |= Regexp::IGNORECASE
            when 'm' then options |= Regexp::MULTILINE
            when 'n' then options |= Regexp::NOENCODING
            else lang = option
            end
          end
          Regexp.new(*[source, options, lang].compact)
        when "!ruby/range"
          args = o.value.split(/([.]{2,3})/, 2).map { |s|
            accept Nodes::Scalar.new(s)
          }
          args.push(args.delete_at(1) == '...')
          Range.new(*args)
        when /^!ruby\/sym(bol)?:?(.*)?$/
          o.value.to_sym
        else
          @ss.tokenize o.value
        end
      end
      private :deserialize

      def visit_Psych_Nodes_Scalar o
        register o, deserialize(o)
      end

      def visit_Psych_Nodes_Sequence o
        if klass = Psych.load_tags[o.tag]
          instance = klass.allocate

          if instance.respond_to?(:init_with)
            coder = Psych::Coder.new(o.tag)
            coder.seq = o.children.map { |c| accept c }
            instance.init_with coder
          end

          return instance
        end

        case o.tag
        when nil
          register_empty(o)
        when '!omap', 'tag:yaml.org,2002:omap'
          map = register(o, Psych::Omap.new)
          o.children.each { |a|
            map[accept(a.children.first)] = accept a.children.last
          }
          map
        when /^!(?:seq|ruby\/array):(.*)$/
          klass = resolve_class($1)
          list  = register(o, klass.allocate)
          o.children.each { |c| list.push accept c }
          list
        else
          register_empty(o)
        end
      end

=begin
      def complex match
        p :complex => match
      end

      def rational match
        p :rational => match
      end

      def object match
        p :object => [match, (match.string.split(':')[1] || "Object")]
      end

      METHODS = {
          '!ruby/object:Complex'  => :complex,
          '!ruby/object:Rational' => :rational,
          '!ruby/object'          => :object,
      }

      re = %r{
  ^!ruby/object:(?:Complex|Rational)$ |
  ^!ruby/object
}x

      [
          '!ruby/object:Complex',
          '!ruby/object:Rational',
          '!ruby/object:MyObject',
          '!ruby/object',
      ].each do |str|
        match = re.match(str)
        send METHODS[match.to_s], match
      end
=end

      REVIVE = {
        '!ruby/struct' => :revive_struct,
        '!ruby/array' => :revive_array,
        '!ruby/object' => :revive_object,
        '!ruby/exception' => :revive_exception,
        '!ruby/hash' => :revive_hash,
        '!ruby/object:Complex' => :revive_complex,
        '!ruby/object:Rational' => :revive_rational
      }

      def visit_Psych_Nodes_Mapping o
        return revive(Psych.load_tags[o.tag], o) if Psych.load_tags[o.tag]
        return revive_hash({}, o) unless o.tag

        case o.tag
        when /^(!ruby\/(?:array|struct|object|exception)):?(.*)$/
          send REVIVE.key?("#{$1}:#{$2}") ? REVIVE["#{$1}:#{$2}"] : REVIVE[$1], o, $2

        when /^!(?:str|ruby\/string)(?::(.*))?/, 'tag:yaml.org,2002:str'
          revive_string(o, $1)

        when '!ruby/range'
          revive_range(o)

        when '!set', 'tag:yaml.org,2002:set'
          revive_set(o)

        when /^!map:(.*)$/, /^!ruby\/hash:(.*)$/
          revive_hash resolve_class($1).new, o

        when '!omap', 'tag:yaml.org,2002:omap'
          revive_map(o)

        else
          revive_hash({}, o)
        end
      end

      def visit_Psych_Nodes_Document o
        accept o.root
      end

      def visit_Psych_Nodes_Stream o
        o.children.map { |c| accept c }
      end

      def visit_Psych_Nodes_Alias o
        @st.fetch(o.anchor) { raise BadAlias, "Unknown alias: #{o.anchor}" }
      end

      private
      def register node, object
        @st[node.anchor] = object if node.anchor
        object
      end

      def register_empty object
        list = register(object, [])
        object.children.each { |c| list.push accept c }
        list
      end

      def revive_hash hash, o
        @st[o.anchor] = hash if o.anchor

          o.children.each_slice(2) { |k,v|
          key = accept(k)

          if key == '<<'
            case v
            when Nodes::Alias
              hash.merge! accept(v)
            when Nodes::Sequence
              accept(v).reverse_each do |value|
                hash.merge! value
              end
            else
              hash[key] = accept(v)
            end
          else
            hash[key] = accept(v)
          end

        }
        hash
      end

      def revive klass, node
        s = klass.allocate
        @st[node.anchor] = s if node.anchor
        h = Hash[*node.children.map { |c| accept c }]
        init_with(s, h, node)
      end

      def init_with o, h, node
        c = Psych::Coder.new(node.tag)
        c.map = h

        if o.respond_to?(:init_with)
          o.init_with c
        elsif o.respond_to?(:yaml_initialize)
          if $VERBOSE
            warn "Implementing #{o.class}#yaml_initialize is deprecated, please implement \"init_with(coder)\""
          end
          o.yaml_initialize c.tag, c.map
        else
          h.each { |k,v| o.instance_variable_set(:"@#{k}", v) }
        end
        o
      end

      # Convert +klassname+ to a Class
      def resolve_class klassname
        return nil unless klassname and not klassname.empty?

        name    = klassname
        retried = false

        begin
          path2class(name)
        rescue ArgumentError, NameError => ex
          unless retried
            name    = "Struct::#{name}"
            retried = ex
            retry
          end
          raise retried
        end
      end

      def revive_struct object, match
        klass = resolve_class(match)

        if klass
          s = register(object, klass.allocate)

          members = {}
          struct_members = s.members.map { |x| x.to_sym }
          object.children.each_slice(2) do |k,v|
            member = accept(k)
            value  = accept(v)
            if struct_members.include?(member.to_sym)
              s.send("#{member}=", value)
            else
              members[member.to_s.sub(/^@/, '')] = value
            end
          end
          init_with(s, members, object)
        else
          members = object.children.map { |c| accept c }
          h = Hash[*members]
          Struct.new(*h.map { |k,v| k.to_sym }).new(*h.map { |k,v| v })
        end
      end

      def revive_object object, match
        name = match || 'Object'

        obj = revive((resolve_class(name) || Object), object)
        obj
      end

      def revive_complex object, match
        h = Hash[*object.children.map { |c| accept c }]
        register object, Complex(h['real'], h['image'])
      end

      def revive_rational object, match
        h = Hash[*object.children.map { |c| accept c }]
        register object, Rational(h['numerator'], h['denominator'])
      end

      def revive_string object, match
        klass = resolve_class(match)
        members = Hash[*object.children.map { |c| accept c }]
        string = members.delete 'str'

        if klass
          string = klass.allocate.replace string
          register(object, string)
        end

        init_with(string, members.map { |k,v| [k.to_s.sub(/^@/, ''),v] }, object)
      end

      def revive_array object, match
        klass = resolve_class(match)
        list  = register(object, klass.allocate)

        members = Hash[object.children.map { |c| accept c }.each_slice(2).to_a]
        list.replace members['internal']

        members['ivars'].each do |ivar, v|
          list.instance_variable_set ivar, v
        end
        list
      end

      def revive_range object
        h = Hash[*object.children.map { |c| accept c }]
        register object, Range.new(h['begin'], h['end'], h['excl'])
      end

      def revive_exception object, match
        h = Hash[*object.children.map { |c| accept c }]

        e = build_exception((resolve_class(match) || Exception),
                            h.delete('message'))
        init_with(e, h, object)
      end

      def revive_set object
        set = Psych::Set.new
        @st[object.anchor] = set if object.anchor
        object.children.each_slice(2) do |k,v|
          set[accept(k)] = accept(v)
        end
        set
      end

      def revive_map object
        map = register(object, Psych::Omap.new)
        object.children.each_slice(2) do |l,r|
          map[accept(l)] = accept r
        end
        map
      end
    end
  end
end
